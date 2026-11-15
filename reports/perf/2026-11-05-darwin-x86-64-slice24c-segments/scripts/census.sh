#!/bin/zsh
# The slice-24c census (design ~/tcg-scratch/s24c-design/README.md §7): one
# release bridge built from the lane worktree wt-s24c at the fixed head
# (build_bridge.t011.sh), then the O2, O0 and O3 `core` proof censuses from
# that dylib (census_t011_dylib.sh, tags o2-s24c, o0-s24c and o3-s24c), then
# the read-only comparison, analyse.sh (which can be rerun on its own).
#
# Baselines: slice 25's censuses census-o2-s25 and census-o0-s25 (head
# d92b944fe, dylib runs/o2-s25.dylib, whose O2 objects equal the base
# a617488aa's: OD-230/231 change no core O2 object and OD-232's knobs are off
# by default). No O3 baseline exists; for O3 only the design's three counts
# are recorded (o3_counts.py).
#
# Run as: BUILD_SLOT_MEM_GB=6 build-slot -- zsh census.sh
S=${0:A:h}
W=$HOME/tcg-scratch/wt-s24c
WANT=38feaf386994a0191efd78440f7a26a8b270cd9d
R=$HOME/tcg-scratch/runs
# The bridge builds in its own tree's target directory (build_bridge.t011.sh);
# a leaked CARGO_TARGET_DIR would hand the census another tree's dylib.
unset CARGO_TARGET_DIR
at_head() { [ "$(git -C $W rev-parse HEAD)" = "$WANT" ]; }
# The bridge's build inputs must be the committed head's, untracked files
# included (docs may move).
inputs_clean() {
  [ -z "$(git -C $W status --porcelain -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo)" ]
}
at_head || { echo "wt-s24c is not at $WANT"; exit 3; }
inputs_clean || { echo "uncommitted build inputs in $W"; exit 3; }
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
STAMP=$(mktemp); sleep 1
echo "bridge build $(date +%H:%M:%S) at $(git -C $W rev-parse HEAD)"
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 3; }
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 3; }
at_head || { echo "wt-s24c moved during the bridge build"; exit 3; }
inputs_clean || { echo "build inputs changed during the bridge build"; exit 3; }
echo "bridge done $(date +%H:%M:%S)"
shasum -a 256 "$D"; ls -l "$D"
for opt in 2 0 3; do
  T=o$opt-s24c
  echo "== O$opt $(date +%H:%M:%S) tag $T"
  ~/tcg-scratch/census_t011_dylib.sh "$D" $T $opt || echo "O$opt census rc=$?"
  # Every census copies the same dylib; each copy must be the built one.
  cmp -s "$D" $R/$T.dylib && echo "O$opt dylib copy identical" || echo "O$opt dylib copy DIFFERS"
done
at_head || echo "wt-s24c moved during the censuses"
zsh $S/analyse.sh; echo "analyse rc=$?"
echo "CENSUS-S24C-DONE $(date +%H:%M:%S)"
