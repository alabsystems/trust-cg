#!/bin/zsh
# The slice-24a census: one release bridge built from the lane worktree at its
# committed head (build_bridge.t011.sh), then the O2 and O0 `core` proof
# censuses from that dylib (census_t011_dylib.sh), each compared with the
# census-o2-7ee0 / census-o0-7ee0 baselines by slice 15's census_compare.py.
# Run as: BUILD_SLOT_MEM_GB=6 build-slot -- zsh census.sh
W=$HOME/tcg-scratch/wt-s24a
unset CARGO_TARGET_DIR
# The bridge's build inputs must be the committed head's (docs may move).
[ -z "$(git -C $W status --porcelain --untracked-files=no -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo)" ] || { echo "uncommitted build inputs in $W"; exit 3; }
STAMP=$(mktemp); sleep 1
echo "bridge build $(date +%H:%M) at $(git -C $W rev-parse HEAD)"
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 3; }
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 3; }
C=$W/reports/perf/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py
# OPTS (default "2 0") picks the opt levels; SUFFIX names a rerun's tags.
for opt in ${=${OPTS:-2 0}}; do
  T=o$opt-s24a${SUFFIX:-}
  echo "== O$opt $(date +%H:%M) tag $T"
  ~/tcg-scratch/census_t011_dylib.sh "$D" $T $opt || echo "O$opt census rc=$?"
  python3 -I $C ~/tcg-scratch/runs/census-o$opt-7ee0 ~/tcg-scratch/runs/census-$T \
    ~/tcg-scratch/s24a-run/census/o$opt${SUFFIX:-} || echo "O$opt compare rc=$?"
  python3 -I $(dirname $0)/census_merged.py ~/tcg-scratch/runs/census-o$opt-7ee0 ~/tcg-scratch/runs/census-$T \
    || echo "O$opt merged attribution rc=$?"
done
echo "CENSUS-CHAIN-DONE $(date +%H:%M)"
