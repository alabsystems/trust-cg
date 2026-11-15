#!/bin/bash
# The fails-before record of OD-233: copy the fixture section of the lane's
# COMMIT <lane-sha> into a helper worktree (make_fails_before.py), then run
# its recorder tests there (od233_fails_before; for `base` also
# od233_base_digests), in the helper's OWN target dir. Kind `base` is the
# slice-25 base b30110fcd (~/tcg-scratch/wt-od233-base), kind `pre` the
# commit before slice 25, 12ebba653 (~/tcg-scratch/wt-od233-pre); the script
# refuses a helper at any other commit, or with any change but the two files
# the generator writes. The copy and the log are kept under
# ~/tcg-scratch/od233-run/. Run under build-slot:
#   BUILD_SLOT_MEM_GB=6 build-slot -- bash fails_before.sh base|pre <lane-sha>
set -u
KIND=$1
LANE_SHA=$2
case "$KIND" in
  base) EXPECT=b30110fcd ;;
  pre) EXPECT=12ebba653 ;;
  *) echo "kind must be base or pre"; exit 2 ;;
esac
LANE=$HOME/tcg-scratch/wt-od233
HELPER=$HOME/tcg-scratch/wt-od233-$KIND
RUN=$HOME/tcg-scratch/od233-run
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
GEN=crates/trust-cg-verify/src/x86_source_bound_body_od233_tests.rs
REG=crates/trust-cg-verify/src/x86_source_bound_body_tests.rs
HEAD=$(git -C "$HELPER" rev-parse HEAD) || exit 9
case "$HEAD" in
  "$EXPECT"*) ;;
  *) echo "the $KIND helper is at $HEAD, not $EXPECT"; exit 3 ;;
esac
LANE_FULL=$(git -C "$LANE" rev-parse --verify "$LANE_SHA^{commit}") || exit 9
OTHER=$(git -C "$HELPER" status --porcelain | grep -v -x -e "?? $GEN" -e " M $REG")
[ -z "$OTHER" ] || { echo "the $KIND helper has other changes:"; echo "$OTHER"; exit 3; }
mkdir -p "$RUN/fails-before" "$RUN/logs"
python3 -I "$LANE/reports/perf/2026-11-05-darwin-x86-64-od233-defined-cut-inputs/fails-before/make_fails_before.py" \
  "$LANE" "$LANE_FULL" "$HELPER" "$KIND" || exit 9
cp "$HELPER/$GEN" "$RUN/fails-before/$KIND-x86_source_bound_body_od233_tests.rs"
echo "== fails-before $KIND at $HEAD (lane commit $LANE_FULL) $(date +%H:%M)"
cd "$HELPER" || exit 9
export TRUST_TARGO=$OV/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-$KIND-own
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- \
  x86_source_bound_body::tests::od233::od233_ --nocapture --test-threads=1
echo "fails-before-exit=$? $KIND $(date +%H:%M)"
