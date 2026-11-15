#!/bin/zsh
# The read-only comparison of the slice-24c censuses (census.sh's last step;
# rerun on its own: it reads census directories only, no build, no slot).
#
# O2 and O0 against slice 25's censuses (census-o2-s25, census-o0-s25) by
# slice 15's census_compare.py and slice 24a's census_merged.py. For O2 also
# the first-refusal classes of both sides (the in-tree root_classes.py, with
# its slice-24c key; the copy beside this script is the ceiling's, kept byte
# for byte) and census_segments.py (the segments= attribution and
# the ceiling cross-check against census-o2k-s25-nifc). For O0 the byte
# comparison of the failed-root and typed-refusal records and slice 25's
# function-by-function trace check (trace_diff.py, copied byte for byte from
# slice 25's record; its S25.0 strip is a no-op here, since neither O0 census
# has a stack-slot scan line), with the unkeyed replay lines attributed to
# functions (o0_outcomes.py). For O3 only the design's three counts
# (o3_counts.py). Then the stop rule over all three (stop_rule.py).
#
# Run as: zsh analyse.sh   (outputs in ~/tcg-scratch/s24c-run/census/{o2,o0,o3})
S=${0:A:h}
# The tree holding this script (its in-tree census_compare.py and census_merged.py).
W=${S:h:h:h:h}
# Overridable for a dry run on other census directories.
R=${R:-$HOME/tcg-scratch/runs}
OUT=${OUT:-$HOME/tcg-scratch/s24c-run/census}
P=$W/reports/perf
C=$P/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py
M=$P/2026-11-04-darwin-x86-64-slice24a-chain-quotient/scripts/census_merged.py
RC=$P/2026-09-27-darwin-x86-64-census/root_classes.py
CEIL=$HOME/tcg-scratch/s24c-run/census/nifc/ceiling/roots.tsv
for opt in 2 0; do
  NEW=$R/census-o$opt-s24c
  BASE=$R/census-o$opt-s25
  O=$OUT/o$opt
  [ -f $NEW/failed_roots.jsonl ] || { echo "O$opt: no census at $NEW"; continue; }
  mkdir -p $O
  echo "== O$opt: $BASE -> $NEW"
  grep -E 'failed roots|wall' $R/census-o$opt-s24c.out | head -3
  python3 -I $C $BASE $NEW $O || echo "O$opt compare rc=$?"
  python3 -I $M $BASE $NEW > $O/merged.txt || echo "O$opt merged attribution rc=$?"
  cat $O/merged.txt
  if [ $opt = 2 ]; then
    python3 -I $RC $BASE > $O/root_classes.base.txt || echo "O2 baseline root classes rc=$?"
    python3 -I $RC $NEW > $O/root_classes.txt || echo "O2 root classes rc=$?"
    echo "-- root classes (baseline)"; cat $O/root_classes.base.txt
    echo "-- root classes (new)"; cat $O/root_classes.txt
    echo "-- segments"
    python3 -I $S/census_segments.py $BASE $NEW $O/segments $CEIL $RC || echo "O2 segments rc=$?"
  else
    for f in failed_roots.jsonl refusals.jsonl; do
      cmp $BASE/$f $NEW/$f && echo "O0 $f byte-identical" || echo "O0 $f DIFFERS"
    done
    python3 -I $S/trace_diff.py $BASE $NEW $O/trace_diff > $O/trace_diff.txt; echo "O0 trace_diff rc=$?"
    cat $O/trace_diff.txt
    # The unkeyed replay lines, attributed to the function each precedes.
    python3 -I $S/o0_outcomes.py $BASE $NEW > $O/outcomes.txt; echo "O0 outcomes rc=$?"
    cat $O/outcomes.txt
  fi
done
if [ -f $R/census-o3-s24c/failed_roots.jsonl ]; then
  mkdir -p $OUT/o3
  echo "== O3: $R/census-o3-s24c (no baseline: the design's three counts only)"
  python3 -I $S/o3_counts.py $R/census-o3-s24c > $OUT/o3/o3_counts.txt || echo "O3 counts rc=$?"
  cat $OUT/o3/o3_counts.txt
else
  echo "O3: no census at $R/census-o3-s24c"
fi
for opt in 2 0 3; do grep -H 'wall' $R/census-o$opt-s24c.out 2>/dev/null; done
python3 -I $S/stop_rule.py $R $OUT > $OUT/stop_rule.txt; echo "stop_rule rc=$?"
cat $OUT/stop_rule.txt
