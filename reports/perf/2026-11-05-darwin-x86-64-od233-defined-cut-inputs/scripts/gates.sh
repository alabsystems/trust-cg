#!/bin/zsh
# The gates of the OD-233 lane on its committed head: gate 1 (the solver-free
# x86 body suite), gate 2 (the od233 module with --nocapture, then its two
# qualification lanes, one per process), gate 3 (slice 25's three and the
# eleven slice-22 to 24 qualification lanes, one per process), gate 4 (the
# codegen body and must-refuse targets, the five x86 e2e execution targets
# and e2e_x86_64_sib_rmw) and gate 5 (trust-cg-lower --lib). The lane tree
# builds in its OWN target dir (stage1-targets/wt-od233-own). Run as:
#   BUILD_SLOT_MEM_GB=6 build-slot -- zsh gates.sh > ~/tcg-scratch/od233-run/logs/gates.log 2>&1
W=$HOME/tcg-scratch/wt-od233
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
DUMP=$HOME/tcg-scratch/od233-run/qual-dump
cd $W || exit 9
export TRUST_TARGO=$OV/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
HEAD=$(git rev-parse HEAD)
echo "== gates at $HEAD $(date +%H:%M)"
[ -z "$(git status --porcelain --untracked-files=no -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo scripts)" ] \
  || { echo "uncommitted build inputs in $W"; exit 3; }
verify() { bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- "$@"; }
P=x86_source_bound_body::tests
echo "== gate1 $(date +%H:%M)"
verify $P:: --skip negative_memo --skip host_qualification --skip verifier_credits --skip canonical_migration
echo "gate1-exit=$?"
echo "== gate2 module $(date +%H:%M)"
verify $P::od233:: --nocapture
echo "gate2-module-exit=$?"
qual() {
  for t in "$@"; do
    echo "-- $t $(date +%H:%M)"
    TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
      TCG_X86_BODY_QUALIFY_DUMP=$DUMP \
      verify "$t" --exact --test-threads=1 --nocapture
    echo "qual-exit=$? $t"
  done
}
echo "== gate2 qualification $(date +%H:%M)"
qual \
  $P::od233_qualification::host_qualification_replays_the_od233_parts \
  $P::od233_qualification::host_qualification_refutes_the_od233_wrong_lowerings
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
echo "== gate4 $(date +%H:%M)"
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  bash scripts/trust_cargo.sh test --no-fail-fast -p trust-cg-codegen --test x86_source_bound_body \
  --test must_refuse_corpus --test e2e_x86_64_differential --test e2e_x86_64_triple_oracle \
  --test e2e_x86_64_mixed_width_shift --test e2e_x86_64_i128_stack_abi \
  --test e2e_x86_64_internal_multi_result --test e2e_x86_64_sib_rmw -j2
echo "gate4-exit=$?"
echo "== gate5 $(date +%H:%M)"
bash scripts/trust_cargo.sh test -p trust-cg-lower --lib -j2
echo "gate5-exit=$?"
[ "$(git rev-parse HEAD)" = "$HEAD" ] \
  && [ -z "$(git status --porcelain --untracked-files=no -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo scripts)" ] \
  && echo "the gates read $HEAD" || echo "WARNING: the tree moved during the gates"
echo "GATES-DONE $(date +%H:%M)"
