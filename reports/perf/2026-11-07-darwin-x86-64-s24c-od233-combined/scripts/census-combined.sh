#!/bin/zsh
# The combined S24c + OD-233 (+ OD-188 division fold) lane's censuses, and S26's step 0
# (~/tcg-scratch/s26-design/scripts/step0.sh) on the same bridge, reordered so the landing's
# censuses come first: bridge, then base (plain O2), o0, o3; then S26's knob runs l, lr, r, all.
# Each census is its own build-slot job, run to completion, one at a time.
# Usage: zsh census-combined.sh <worktree detached at the lane head> <tag>
# Decision 2026-11-07: S26's step 0 runs on the combined LANE head, not on main after landing:
# the landing train's queue is long, and this one bridge serves both the lane's census and step 0.
set -u
WT="${1:?worktree}"; TAG="${2:?tag}"
SHA=$(git -C "$WT" rev-parse HEAD) || exit 9
[ -z "$(git -C "$WT" status --porcelain)" ] || { echo "census-combined: $WT is not clean"; exit 9; }
echo "census-combined: lane head $SHA in $WT, tag $TAG, $(date +%H:%M)"
unset CARGO_TARGET_DIR
DYLIB="$WT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
STAMP=$(mktemp); trap 'rm -f "$STAMP"' EXIT
BUILD=$(BUILD_SLOT_MEM_GB=6 build-slot -- ~/tcg-scratch/build_bridge.t011.sh "$WT" 2>&1)
echo "$BUILD" | tail -5
echo "$BUILD" | grep -q '^EXIT=0$' || { echo "census-combined: bridge build failed"; exit 8; }
[ "$DYLIB" -nt "$STAMP" ] || { echo "census-combined: $DYLIB was not rebuilt by this run"; exit 8; }
shasum -a 256 "$DYLIB"
echo "$SHA $DYLIB" > ~/tcg-scratch/runs/$TAG.bridge-commit.txt
run() {  # <suffix> <opt> [knob...]
  local suffix=$1 opt=$2; shift 2
  echo "== $TAG-$suffix opt=$opt knobs=[$*] queued $(date +%H:%M:%S)"
  BUILD_SLOT_MEM_GB=6 build-slot -- ~/tcg-scratch/census_t011_dylib.sh "$DYLIB" "$TAG-$suffix" "$opt" "$@" | tail -8
  echo "== $TAG-$suffix rc=${pipestatus[1]} $(date +%H:%M:%S)"
}
run base 2
run o0 0
run o3 3
echo LANDING-CENSUSES-DONE
run l 2 no-x86-licm
run lr 2 no-x86-licm no-x86-loop-rotate
run r 2 no-x86-loop-rotate
run all 2 no-x86-licm no-x86-loop-rotate no-x86-ifconvert no-x86-cmov-swap
# S26 step 5: one trust-ir dump of the landing base's core compile (the replicas' source).
run tir 2 dump-trust-ir=$HOME/tcg-scratch/runs/tir-$TAG
CMP=$HOME/trust-cg/reports/perf/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py
for s in l r lr all; do
  python3 -I "$CMP" ~/tcg-scratch/runs/census-$TAG-base ~/tcg-scratch/runs/census-$TAG-$s \
    ~/tcg-scratch/runs/compare-$TAG-base-vs-$s > /dev/null && echo "compared base vs $s"
done
grep 'fn=_RNvNtCs7e1ihmkzmZ8_4core3str19slice_error_fail_rt ' ~/tcg-scratch/runs/census-$TAG-l/stderr.log | cut -c1-300
echo STEP0-DONE
