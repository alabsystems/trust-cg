#!/bin/zsh
# The review round's final job on the committed lane head (run under
# build-slot, one job): (1) the release bridge from the head and the O2 and
# O0 `core` proof censuses from it, compared with the slice-24a baselines;
# (2) the fails-before record: crates/trust-cg-verify/src checked out at
# 6c036f1de (slice 25.0) in the lane tree, the recorder copied in by
# make_fails_before.py, run, and the tree restored to the head; (3) gates
# 1 to 4 and the slice-25 qualification lanes on the restored head.
W=$HOME/tcg-scratch/wt-s25
L=$HOME/tcg-scratch/s25-run/fix/logs
R=$W/reports/perf/2026-11-04-darwin-x86-64-slice25-sib-rows
OUT=$HOME/tcg-scratch/s25-run/fix/census
BASE2=$HOME/tcg-scratch/runs/census-o2-s24a-f
BASE0=$HOME/tcg-scratch/runs/census-o0-s24a
BASEREV=6c036f1de27e70e9cca4dcc973ada6434c6f249d
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
HEAD=$(git -C $W rev-parse HEAD)
mkdir -p $L $OUT
echo "== fin at $HEAD $(date +%H:%M)"
[ -z "$(git -C $W status --porcelain --untracked-files=no)" ] || { echo "uncommitted changes in $W"; exit 3; }

if [ -z "$SKIP_CENSUS" ]; then
  # (1) The bridge from the committed head, then the censuses.
  STAMP=$(mktemp); sleep 1
  echo "== bridge $(date +%H:%M)"
  BOUT=$(env -u CARGO_TARGET_DIR ~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
  echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 4; }
  D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
  [ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 4; }
  [ "$(git -C $W rev-parse HEAD)" = "$HEAD" ] || { echo "head moved during the bridge build"; exit 4; }
  shasum -a 256 "$D"
  for T in o2-s25f:2 o0-s25f:0; do
    TAG=${T%%:*}; OPT=${T##*:}
    echo "== census $TAG $(date +%H:%M)"
    ~/tcg-scratch/census_t011_dylib.sh "$D" $TAG $OPT || echo "census $TAG rc=$?"
  done
  python3 -I $W/reports/perf/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py \
    $BASE2 $HOME/tcg-scratch/runs/census-o2-s25f $OUT/compare-o2 || echo "compare o2 rc=$?"
  python3 -I $W/reports/perf/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py \
    $BASE0 $HOME/tcg-scratch/runs/census-o0-s25f $OUT/compare-o0 || echo "compare o0 rc=$?"
  python3 -I $R/scripts/trace_diff.py $BASE2 $HOME/tcg-scratch/runs/census-o2-s25f $OUT/trace_diff-o2 \
    > $OUT/trace_diff-o2.txt; echo "trace_diff o2 rc=$?"; cat $OUT/trace_diff-o2.txt
  python3 -I $R/scripts/trace_diff.py $BASE0 $HOME/tcg-scratch/runs/census-o0-s25f $OUT/trace_diff-o0 \
    > $OUT/trace_diff-o0.txt; echo "trace_diff o0 rc=$?"; cat $OUT/trace_diff-o0.txt
  python3 -I $W/reports/perf/2026-11-04-darwin-x86-64-slice24a-chain-quotient/scripts/census_merged.py \
    $BASE2 $HOME/tcg-scratch/runs/census-o2-s25f > $OUT/merged-o2.txt || echo "merged rc=$?"
  cat $OUT/merged-o2.txt
  for d in $OUT/compare-o2 $OUT/compare-o0; do echo "-- $d"; ls $d; head -40 $d/*.md 2>/dev/null; done
fi

# (2) The fails-before record in the lane tree, restored on any exit.
restore() {
  git -C $W checkout HEAD -- crates/trust-cg-verify/src
  echo "restored: $(git -C $W status --porcelain --untracked-files=no | wc -l | tr -d ' ') changed paths"
}
echo "== fails-before $(date +%H:%M)"
trap restore EXIT
git -C $W checkout $BASEREV -- crates/trust-cg-verify/src || exit 5
python3 -I $R/fails-before/make_fails_before.py $W $W || exit 5
cp $W/crates/trust-cg-verify/src/x86_source_bound_body_slice25_tests.rs $L/copy5_x86_source_bound_body_slice25_tests.rs
source ~/tcg-scratch/s25-run/fix/scripts/env.sh
verify x86_source_bound_body::tests::slice25::s25_fails_before --nocapture
echo "fails-before-exit=$?"
restore
trap - EXIT
[ -z "$(git -C $W status --porcelain --untracked-files=no)" ] || { echo "the tree is not the head after the fails-before record"; exit 6; }

# (3) Gates 1 to 4 and the slice-25 lanes on the head.
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
      TCG_X86_BODY_QUALIFY_DUMP=$HOME/tcg-scratch/s25-run/fix/qual-dump \
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
[ "$(git -C $W rev-parse HEAD)" = "$HEAD" ] && [ -z "$(git -C $W status --porcelain --untracked-files=no)" ] \
  && echo "the gates read $HEAD" || echo "WARNING: the tree moved during the gates"
echo "FIN-DONE $(date +%H:%M)"
