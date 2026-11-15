#!/bin/zsh
# The gates on the merged head (slice 25 with origin/main 12ebba653 merged
# in), run before the docs commit and again by the landing train: gate 1
# (the solver-free x86 body suite), gate 2 (the slice-25 module with
# --nocapture, then its three qualification lanes, one per process), gate 3
# (the eleven slice-22 to 24 qualification lanes, one per process) and gate
# 4 (the codegen body and must-refuse targets, the five x86 e2e execution
# targets and e2e_x86_64_sib_rmw). The lane tree builds in its OWN target dir
# (stage1-targets/wt-s25-own, the landing train's): the dir the fails-before
# base tree once shared is not used. Run as: build-slot -- zsh gates.sh
W=$HOME/tcg-scratch/wt-s25
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
cd $W || exit 9
export TRUST_TARGO=$OV/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s25-own
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
verify $P::slice25:: --nocapture
echo "gate2-module-exit=$?"
qual() {
  for t in "$@"; do
    echo "-- $t $(date +%H:%M)"
    TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
      TCG_X86_BODY_QUALIFY_DUMP=$HOME/tcg-scratch/s25-run/merged/qual-dump \
      verify "$t" --exact --test-threads=1 --nocapture
    echo "qual-exit=$? $t"
  done
}
echo "== gate2 qualification $(date +%H:%M)"
qual \
  $P::slice25_qualification::host_qualification_replays_the_slice_twenty_five_body_theorems \
  $P::slice25_qualification::host_qualification_refutes_the_slice_twenty_five_wrong_lowerings \
  $P::slice25_qualification::verifier_credits_every_bound_slice_twenty_five_row_with_the_replayed_body_theorem
echo "== gate3 $(date +%H:%M)"
qual \
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
  --test e2e_x86_64_internal_multi_result --test e2e_x86_64_sib_rmw -j2 -- --nocapture
echo "gate4-exit=$?"
[ "$(git rev-parse HEAD)" = "$HEAD" ] \
  && [ -z "$(git status --porcelain --untracked-files=no -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo scripts)" ] \
  && echo "the gates read $HEAD" || echo "WARNING: the tree moved during the gates"
echo "GATES-DONE $(date +%H:%M)"
