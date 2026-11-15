#!/bin/zsh
# The slice-24c gates on the lane tree: gate 1 (the solver-free x86 body
# suite), gate 2 (the slice-24c module with --nocapture, then its three
# qualification lanes, one per process), gate 3 (the fourteen slice-22 to 25
# qualification lanes, one per process), gate 4 (the codegen body and
# must-refuse targets and the six x86 e2e execution targets) and gate 5
# (trust-cg-lower --lib). The tree builds in its OWN target dir
# (stage1-targets/wt-s24c-own). Run as: BUILD_SLOT_MEM_GB=6 build-slot -- zsh gates.sh
# Optional: GATES="1 2 3 4 5" selects gates; DUMP=<dir> is where the
# qualification lanes dump their queries (default s24c-run/qual-dump).
W=$HOME/tcg-scratch/wt-s24c
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
cd $W || exit 9
export TRUST_TARGO=$OV/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s24c-own
GATES=${GATES:-"1 2 3 4 5"}
HEAD=$(git rev-parse HEAD)
echo "== gates at $HEAD $(date +%H:%M) [$GATES]"
verify() { bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- "$@"; }
P=x86_source_bound_body::tests
qual() {
  for t in "$@"; do
    echo "-- $t $(date +%H:%M)"
    TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
      TCG_X86_BODY_QUALIFY_DUMP=${DUMP:-$HOME/tcg-scratch/s24c-run/qual-dump} \
      verify "$t" --exact --test-threads=1 --nocapture
    echo "qual-exit=$? $t"
  done
}
if [[ " $GATES " == *" 1 "* ]]; then
  echo "== gate1 $(date +%H:%M)"
  verify $P:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration
  echo "gate1-exit=$?"
fi
if [[ " $GATES " == *" 2 "* ]]; then
  echo "== gate2 module $(date +%H:%M)"
  verify $P::slice24c:: --nocapture
  echo "gate2-module-exit=$?"
  echo "== gate2 qualification $(date +%H:%M)"
  qual \
    $P::slice24c_qualification::host_qualification_replays_the_slice_twenty_four_c_body_theorems \
    $P::slice24c_qualification::host_qualification_refutes_the_slice_twenty_four_c_wrong_lowerings \
    $P::slice24c_qualification::verifier_credits_every_bound_slice_twenty_four_c_row_with_the_replayed_body_theorem
fi
if [[ " $GATES " == *" 3 "* ]]; then
  echo "== gate3 $(date +%H:%M)"
  qual \
    $P::slice25_qualification::host_qualification_replays_the_slice_twenty_five_body_theorems \
    $P::slice25_qualification::host_qualification_refutes_the_slice_twenty_five_wrong_lowerings \
    $P::slice25_qualification::verifier_credits_every_bound_slice_twenty_five_row_with_the_replayed_body_theorem \
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
fi
if [[ " $GATES " == *" 4 "* ]]; then
  echo "== gate4 $(date +%H:%M)"
  TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
    bash scripts/trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body \
    --test must_refuse_corpus --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle \
    --test e2e_x86_64_mixed_width_shift --test e2e_x86_64_i128_stack_abi \
    --test e2e_x86_64_internal_multi_result --test e2e_x86_64_sib_rmw -j2
  echo "gate4-exit=$?"
fi
if [[ " $GATES " == *" 5 "* ]]; then
  echo "== gate5 $(date +%H:%M)"
  bash scripts/trust_cargo.sh test -p trust-cg-lower --lib -j2
  echo "gate5-exit=$?"
fi
[ "$(git rev-parse HEAD)" = "$HEAD" ] && echo "the gates read $HEAD" || echo "WARNING: HEAD moved during the gates"
echo "GATES-DONE $(date +%H:%M)"
