#!/bin/zsh
# The slice-25.0 diagnostic census (design ~/tcg-scratch/s25-design/README.md
# §7): one release bridge built from the detached worktree wt-s25d at the S25.0
# commit (build_bridge.t011.sh), the O2 `core` proof census from that dylib
# (census_t011_dylib.sh, tag o2-s25d), then slice 15's census_compare.py and
# slice 24a's census_merged.py against the O2 baseline census-o2-s24a-f (built
# at b342de091; its build inputs differ from 6c036f1de only by S25.0 and the
# default-off opt-out knobs of 85d236b37).
# Run as: BUILD_SLOT_MEM_GB=6 build-slot -- zsh census_diag.sh
W=$HOME/tcg-scratch/wt-s25d
WANT=6c036f1de27e70e9cca4dcc973ada6434c6f249d
BASE=$HOME/tcg-scratch/runs/census-o2-s24a-f
OUT=$HOME/tcg-scratch/s25-run/census/diag
T=o2-s25d
unset CARGO_TARGET_DIR
[ "$(git -C $W rev-parse HEAD)" = "$WANT" ] || { echo "wt-s25d is not at $WANT"; exit 3; }
# The bridge's build inputs must be the committed head's.
[ -z "$(git -C $W status --porcelain --untracked-files=no -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo)" ] || { echo "uncommitted build inputs in $W"; exit 3; }
STAMP=$(mktemp); sleep 1
echo "bridge build $(date +%H:%M) at $(git -C $W rev-parse HEAD)"
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 3; }
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 3; }
shasum -a 256 "$D"
echo "== O2 $(date +%H:%M) tag $T"
~/tcg-scratch/census_t011_dylib.sh "$D" $T 2 || { echo "O2 census rc=$?"; exit 4; }
mkdir -p $OUT
python3 -I $W/reports/perf/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py \
  $BASE ~/tcg-scratch/runs/census-$T $OUT/compare || echo "compare rc=$?"
python3 -I $W/reports/perf/2026-11-04-darwin-x86-64-slice24a-chain-quotient/scripts/census_merged.py \
  $BASE ~/tcg-scratch/runs/census-$T > $OUT/merged.txt || echo "merged attribution rc=$?"
cat $OUT/merged.txt
echo "CENSUS-DIAG-DONE $(date +%H:%M)"
