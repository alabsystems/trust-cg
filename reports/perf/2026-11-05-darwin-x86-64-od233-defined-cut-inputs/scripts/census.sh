#!/bin/zsh
# The OD-233 census (design ~/tcg-scratch/od233-design/README.md §7): one
# release bridge built from the lane worktree wt-od233 at the fixed head
# (build_bridge.t011.sh), then the O2 and O0 `core` proof censuses from that
# dylib (census_t011_dylib.sh, tags o2-od233 and o0-od233), each compared
# with slice 25's censuses (census-o2-s25, census-o0-s25, both from
# o2-s25.dylib, built at d92b944fe) by slice 15's census_compare.py,
# root_classes.py, this record's parts_census.py and census233.py (the stop
# rule's items, the trace of core::wtf8::slice_error_fail, the cut_pairing
# texts) and an object comparison. For O0 also the byte comparison of the
# failed-root and typed-refusal records and slice 25's trace_diff.py.
#
# Per-part times: slice 25's censuses ran without the `solve-trace` knob, so
# they carry no per-part AY or Clean time. Both OD-233 censuses run with it
# (`-Ztrust-ir-cg-args=solve-trace`, a diagnostic that prints one line per
# solve and changes no decision), and each is paired with a re-run of the
# baseline dylib with the same knob (tags o2-s25-st, o0-s25-st), run right
# after it: part_times.py attributes the solve and check lines to their
# function's parts and compares the pair. The re-runs are also compared with
# census-o2-s25/census-o0-s25, which checks that the knob changes no record.
# Run as:
#   BUILD_SLOT_MEM_GB=6 build-slot -- zsh census.sh > ~/tcg-scratch/od233-run/logs/census.log 2>&1
S=${0:A:h}
W=$HOME/tcg-scratch/wt-od233
WANT=c76048fa3ffbe92855c132cf69566046bdba3878
OUT=$HOME/tcg-scratch/od233-run/census
RUNS=$HOME/tcg-scratch/runs
P=$W/reports/perf
C=$P/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py
RC=$P/2026-09-27-darwin-x86-64-census/root_classes.py
TD=$P/2026-11-04-darwin-x86-64-slice25-sib-rows/scripts/trace_diff.py
# The baselines' own dylib (d92b944fe; SHA-256 2e47fae1…, as o0-s25.dylib).
BASE_DYLIB=$RUNS/o2-s25.dylib
BASE_SHA=2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2
STORE=$HOME/.cache/trust-cg/alethe-certs
unset CARGO_TARGET_DIR
[ "$(git -C $W rev-parse HEAD)" = "$WANT" ] || { echo "wt-od233 is not at $WANT"; exit 3; }
# The bridge's build inputs must be the committed head's, untracked files
# included (docs may move).
[ -z "$(git -C $W status --porcelain -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo)" ] \
  || { echo "uncommitted build inputs in $W"; exit 3; }
for t in o2-od233 o0-od233 o2-s25-st o0-s25-st; do
  [ -e $RUNS/census-$t ] && { echo "census-$t exists; refusing to overwrite it"; exit 3; }
done
[ "$(shasum -a 256 $BASE_DYLIB | cut -d' ' -f1)" = "$BASE_SHA" ] || { echo "baseline dylib changed: $BASE_DYLIB"; exit 3; }
STAMP=$(mktemp); sleep 1
echo "bridge build $(date +%H:%M) at $(git -C $W rev-parse HEAD)"
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT"
echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 3; }
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 3; }
[ "$(git -C $W rev-parse HEAD)" = "$WANT" ] || { echo "wt-od233 moved during the build"; exit 3; }
[ -z "$(git -C $W status --porcelain -- crates Cargo.toml Cargo.lock rust-toolchain.toml .cargo)" ] \
  || { echo "build inputs changed during the build"; exit 3; }
shasum -a 256 "$D"
echo "bridge built $(date +%H:%M)"

census() { # <dylib> <tag> <opt>
  echo "== census $2 (O$3) $(date +%H:%M), load $(sysctl -n vm.loadavg), cert store $(ls $STORE/*.alethecert 2>/dev/null | wc -l | tr -d ' ') entries"
  ~/tcg-scratch/census_t011_dylib.sh "$1" "$2" "$3" solve-trace
  local rc=$?
  echo "census $2 rc=$rc $(date +%H:%M), load $(sysctl -n vm.loadavg), cert store $(ls $STORE/*.alethecert 2>/dev/null | wc -l | tr -d ' ') entries"
  return $rc
}

objcmp() { # <base dir> <new dir>: the emitted objects, by name, byte for byte
  python3 -I - "$1/obj" "$2/obj" <<'EOF'
import filecmp, os, sys
a, b = sys.argv[1:3]
na, nb = set(os.listdir(a)), set(os.listdir(b))
same = sorted(n for n in na & nb if filecmp.cmp(f'{a}/{n}', f'{b}/{n}', shallow=False))
diff = sorted(n for n in na & nb if n not in set(same))
print(f'objects: base {len(na)}, new {len(nb)}, common {len(na & nb)}, byte-identical {len(same)}, '
      f'differing {len(diff)}, only base {len(na - nb)}, only new {len(nb - na)}')
for n in diff: print('  differs:', n)
for n in sorted(na - nb): print('  only base:', n)
for n in sorted(nb - na): print('  only new:', n)
EOF
}

for opt in 2 0; do
  T=o$opt-od233
  BT=o$opt-s25-st
  BASE=$RUNS/census-o$opt-s25
  NEW=$RUNS/census-$T
  O=$OUT/o$opt
  mkdir -p $O
  census "$D" $T $opt || { echo "O$opt census failed"; continue; }
  census "$BASE_DYLIB" $BT $opt || echo "O$opt baseline timing census failed"
  echo "== O$opt analysis $(date +%H:%M) against $BASE"
  python3 -I $C $BASE $NEW $O/compare || echo "O$opt compare rc=$?"
  python3 -I $RC $BASE > $O/root_classes.base.txt || echo "O$opt baseline root classes rc=$?"
  python3 -I $RC $NEW > $O/root_classes.txt || echo "O$opt root classes rc=$?"
  echo "-- root classes (new)"; cat $O/root_classes.txt
  python3 -I $S/parts_census.py $BASE/stderr.log $O/parts.base.json > $O/parts.base.txt || echo "O$opt baseline parts rc=$?"
  python3 -I $S/parts_census.py $NEW/stderr.log $O/parts.json > $O/parts.txt || echo "O$opt parts rc=$?"
  echo "-- parts (baseline)"; head -40 $O/parts.base.txt
  echo "-- parts (new)"; head -60 $O/parts.txt
  python3 -I $S/census233.py $BASE $NEW $O/followup; echo "O$opt census233 rc=$?"
  echo "-- objects"; objcmp $BASE $NEW | tee $O/objects.txt | head -40
  if [ $opt = 0 ]; then
    for f in failed_roots.jsonl refusals.jsonl; do
      cmp $BASE/$f $NEW/$f && echo "O0 $f byte-identical" || echo "O0 $f DIFFERS"
    done
    python3 -I $TD $BASE $NEW $O/trace_diff > $O/trace_diff.txt; echo "O0 trace_diff rc=$?"
    head -60 $O/trace_diff.txt
  fi
  if [ -d $RUNS/census-$BT ]; then
    echo "-- the knob's re-run of the baseline dylib against $BASE"
    python3 -I $C $BASE $RUNS/census-$BT $O/rerun-compare | head -8 || echo "O$opt rerun compare rc=$?"
    for f in failed_roots.jsonl refusals.jsonl; do
      cmp $BASE/$f $RUNS/census-$BT/$f && echo "rerun O$opt $f byte-identical" || echo "rerun O$opt $f DIFFERS"
    done
    python3 -I $S/part_times.py $NEW $RUNS/census-$BT $O/times; echo "O$opt part_times rc=$?"
  fi
done
[ "$(git -C $W rev-parse HEAD)" = "$WANT" ] || echo "NOTE: wt-od233 moved during the censuses"
echo "CENSUS-OD233-DONE $(date +%H:%M)"
