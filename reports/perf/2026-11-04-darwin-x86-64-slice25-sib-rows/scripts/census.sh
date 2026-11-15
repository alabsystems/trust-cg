#!/bin/zsh
# The slice-25 census (design ~/tcg-scratch/s25-design/README.md §7): one
# release bridge built from the lane worktree wt-s25 at the fixed head
# (build_bridge.t011.sh), then the O2 and O0 `core` proof censuses from that
# dylib (census_t011_dylib.sh, tags o2-s25 and o0-s25), each compared with the
# slice-24a censuses of main's code (census-o2-s24a-f, built at b342de091, and
# census-o0-s24a) by slice 15's census_compare.py and attributed to the
# merged-chain quotient by slice 24a's census_merged.py. For O2 also the
# first-refusal classes (root_classes.py) and the S/R first hits
# (firsthit.py) of both sides; for O0 the byte comparison of the failed-root
# and typed-refusal records and slice 25.0's function-by-function trace check
# (trace_diff.py, which strips only the stack-slot scan's row detail).
# Run as: BUILD_SLOT_MEM_GB=6 build-slot -- zsh census.sh
S=${0:A:h}
W=$HOME/tcg-scratch/wt-s25
WANT=d92b944fe8d22ba68cdbe5c32130590b591192bd
OUT=$HOME/tcg-scratch/s25-run/census
P=$W/reports/perf
C=$P/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py
M=$P/2026-11-04-darwin-x86-64-slice24a-chain-quotient/scripts/census_merged.py
RC=$P/2026-09-27-darwin-x86-64-census/root_classes.py
unset CARGO_TARGET_DIR
[ "$(git -C $W rev-parse HEAD)" = "$WANT" ] || { echo "wt-s25 is not at $WANT"; exit 3; }
# The bridge's build inputs must be the committed head's (docs may move).
[ -z "$(git -C $W status --porcelain --untracked-files=no -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo)" ] || { echo "uncommitted build inputs in $W"; exit 3; }
STAMP=$(mktemp); sleep 1
echo "bridge build $(date +%H:%M) at $(git -C $W rev-parse HEAD)"
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 3; }
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 3; }
shasum -a 256 "$D"
for opt in 2 0; do
  T=o$opt-s25
  NEW=$HOME/tcg-scratch/runs/census-$T
  O=$OUT/o$opt
  if [ $opt = 2 ]; then BASE=$HOME/tcg-scratch/runs/census-o2-s24a-f; else BASE=$HOME/tcg-scratch/runs/census-o0-s24a; fi
  echo "== O$opt $(date +%H:%M) tag $T against $BASE"
  ~/tcg-scratch/census_t011_dylib.sh "$D" $T $opt || { echo "O$opt census rc=$?"; continue; }
  mkdir -p $O
  python3 -I $C $BASE $NEW $O || echo "O$opt compare rc=$?"
  python3 -I $M $BASE $NEW > $O/merged.txt || echo "O$opt merged attribution rc=$?"
  cat $O/merged.txt
  if [ $opt = 2 ]; then
    python3 -I $RC $BASE > $O/root_classes.base.txt || echo "O2 baseline root classes rc=$?"
    python3 -I $RC $NEW > $O/root_classes.txt || echo "O2 root classes rc=$?"
    python3 -I $S/firsthit.py $BASE > $O/firsthit.base.txt || echo "O2 baseline first hits rc=$?"
    python3 -I $S/firsthit.py $NEW > $O/firsthit.txt || echo "O2 first hits rc=$?"
    echo "-- root classes (new)"; cat $O/root_classes.txt
    echo "-- first hits (new)"; cat $O/firsthit.txt
  else
    for f in failed_roots.jsonl refusals.jsonl; do
      cmp $BASE/$f $NEW/$f && echo "O0 $f byte-identical" || echo "O0 $f DIFFERS"
    done
    python3 -I $S/trace_diff.py $BASE $NEW $O/trace_diff > $O/trace_diff.txt; echo "O0 trace_diff rc=$?"
    cat $O/trace_diff.txt
  fi
done
echo "CENSUS-S25-DONE $(date +%H:%M)"
